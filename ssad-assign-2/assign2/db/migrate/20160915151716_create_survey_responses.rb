class CreateSurveyResponses < ActiveRecord::Migration[5.0]
  def change
    create_table :survey_responses do |t|
      t.integer :user_id
      t.integer :survey_id
      t.timestamps
    end

    add_reference :answers, :survey_response, foreign_key: true

  end
end

class FixLinkQuestionSurvey < ActiveRecord::Migration[5.0]
  def change
    drop_table :surveys
    drop_table :questions

    create_table :surveys do |t|
      t.string :name

      t.timestamps
    end

    create_table :questions do |t|
      t.string :question
      t.integer :index
      t.belongs_to :surveys, index: true

      t.timestamps
    end

    create_join_table :surveys, :questions
    
  end
end

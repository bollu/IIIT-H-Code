class Answer < ApplicationRecord
    belongs_to :question
    belongs_to :survey_response

    validates :answer, presence: true

end
